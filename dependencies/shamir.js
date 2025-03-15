class Shamir {
  constructor(prime, minSecretLength = 20) {
    this.prime = prime;
    this.minSecretLength = minSecretLength;
  }

  split(secret, quorumCount, sharesCount) {
    sharesCount = parseInt(sharesCount);
    quorumCount = parseInt(quorumCount);
    Shamir.validateInput(secret, quorumCount, sharesCount);
    const secretInt = BigInt(Shamir.string2hex(this.saltSecret(secret)));
    const random = () => Shamir.bigRandom(secretInt.toString(2).length);
    const shares = ShamirEngine.split(secretInt, quorumCount, sharesCount, this.prime, random);
    return shares.map(share => '' + share.getNumber() + ';' + Shamir.bigInt2Base64(share.getShare()));
  }

  combine(sharesBase64) {
    const shares = sharesBase64.map(share => new SecretShare(parseInt(share.split(';')[0]), Shamir.base64ToBigInt(share.split(';')[1])))
    const secretInt = ShamirEngine.combine(shares, this.prime);
    const secretSalted= Shamir.hex2string(secretInt.toString(16));
    return this.unsaltSecret(secretSalted);
  }

  static validateInput(secret, quorumCount, sharesCount) {
    if (!/^[\x20-\x7D]*$/.test(secret)) {
      throw Error('Secret can contain only characters from range 0x20 to 0x7D in ASCII table')
    }
    if (sharesCount < 2 || sharesCount > 10) {
      throw Error(`Shares count is ${sharesCount} but should be in range from 2 to 10 inclusive`)
    }
    if (quorumCount < 2 || quorumCount > sharesCount) {
      throw Error(`Quorum count is ${quorumCount} but should be in range from 2 to shares count ${sharesCount} inclusive`)
    }
  }

  saltSecret(secret) {
    if (secret.includes('~')) {
      throw Error('Secret cannot contain ~ character')
    }
    if (secret.length < this.minSecretLength) {
      return secret + '~' + Shamir.randomString(this.minSecretLength - secret.length);
    } else {
      return secret;
    }
  }

  unsaltSecret(secretSalted) {
    if (secretSalted.includes('~')) {
      return secretSalted.split('~')[0];
    } else {
      return secretSalted;
    }
  }

  static string2hex(text) {
    let hexString = '';
    for (var i = 0; i < text.length; i++) {
      hexString += ("0" + text.charCodeAt(i).toString(16)).slice(-2);
    }
    return '0x' + hexString;
  }

  static hex2string(hex) {
    if (hex.substring(0, 2) === '0x') {
      hex = hex.substring(2);
    }

    let str = '';
    for (let i = 0; i < hex.length; i += 2) {
      const byte = parseInt(hex.substr(i, 2), 16);
      str += String.fromCharCode(byte);
    }

    return str;
  }

  static bigRandom(bitSize) {
    if (bitSize <= 0) {
      throw new Error('Byte size must be greater than 0');
    }

    let output = 0n;
    for (let i = 0; i < bitSize; i++) {
      output *= 2n;
      if (Math.random() < 0.5) {
        output += 0b1n
      }
    }
    return output;
  }

  static bigInt2Base64(number) {
    var hex = BigInt(number).toString(16);
    if (hex.length % 2) {
      hex = '0' + hex;
    }

    var bin = [];
    var i = 0;
    var d;
    var b;
    while (i < hex.length) {
      d = parseInt(hex.slice(i, i + 2), 16);
      b = String.fromCharCode(d);
      bin.push(b);
      i += 2;
    }

    return btoa(bin.join(''));
  }

  static base64ToBigInt(base64) {
    var bin = atob(base64);
    var hex = [];

    bin.split('').forEach(function (ch) {
      var h = ch.charCodeAt(0).toString(16);
      if (h.length % 2) {
        h = '0' + h;
      }
      hex.push(h);
    });

    return BigInt('0x' + hex.join(''));
  }

  static randomString(length) {
    let str = '';
    const allowedCharacters = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
    for (let i = 0; i < length; i ++) {
      str += allowedCharacters[Math.floor(Math.random() * allowedCharacters.length)];
    }
    return str
  }

}

class ShamirEngine {
  static split(secret, needed, available, prime, random) {
    const coeff = new Array(needed);
    coeff[0] = secret;

    for (let i = 1; i < needed; i++) {
      let r;
      while (true) {
        r = BigInt.asUintN(prime.toString(2).length, random());
        if (r > 0 && r < prime) {
          break;
        }
      }
      coeff[i] = r;
    }

    const shares = new Array(available);
    for (let x = 1; x <= available; x++) {
      let accum = secret;

      for (let exp = 1; exp < needed; exp++) {
        accum = (accum + coeff[exp] * BigInt(x ** exp) % prime) % prime;
      }
      shares[x - 1] = new SecretShare(x, accum);
    }

    return shares;
  }

  static combine(shares, prime) {
    let accum = BigInt(0);

    for (let formula = 0; formula < shares.length; formula++) {
      let numerator = BigInt(1);
      let denominator = BigInt(1);

      for (let count = 0; count < shares.length; count++) {
        if (formula === count) continue;

        let startposition = shares[formula].getNumber();
        let nextposition = shares[count].getNumber();

        numerator = (numerator * BigInt(nextposition) * -1n) % prime;
        denominator = (denominator * BigInt(startposition - nextposition)) % prime;
      }
      let value = shares[formula].getShare();
      let tmp = (value * numerator * this.modInverse(denominator, prime)) % prime;
      accum = (prime + accum + tmp) % prime;
    }

    return accum;
  }

  static gcdD(a, b) {
    if (b === 0n) {
      return [a, 1n, 0n];
    } else {
      let n = a / b;
      let c = a % b;
      let r = this.gcdD(b, c);
      return [r[0], r[2], r[1] - r[2] * n];
    }
  }

  static modInverse(k, prime) {
    k = k % prime;
    let r = k < 0 ? this.gcdD(prime, -k)[2] * -1n : this.gcdD(prime, k)[2];
    return (prime + r) % prime;
  }
}

class SecretShare {
  constructor(number, share) {
    this.number = number;
    this.share = share;
  }

  getNumber() {
    return this.number;
  }

  getShare() {
    return this.share;
  }

  toString() {
    return "SecretShare [num=" + this.number + ", share=" + this.share + "]";
  }
}

if (typeof window === 'undefined') {
  module.exports.Shamir = Shamir;
}
