int main1(){
  int f46b, zq, x, bx, q80k, stof, txn, xc;

  f46b=62;
  zq=0;
  x=17;
  bx=10;
  q80k=0;
  stof=f46b;
  txn=f46b;
  xc=-8;

  while (zq<=f46b-1) {
      if (!(q80k!=0)) {
          x = x - 3;
          bx = bx + 3;
          q80k = 0;
      }
      else {
          x = x + 3;
          bx = bx - 3;
          q80k = 1;
      }
      zq++;
      if (zq+2<=xc+f46b) {
          stof += txn;
      }
      txn = txn + zq;
      stof += 2;
      txn += stof;
  }

}
