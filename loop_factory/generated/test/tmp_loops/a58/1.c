int main1(int r){
  int n0e, rw, la, dw6v, mh, n, jn7, j;

  n0e=0;
  rw=(r%20)+10;
  la=(r%15)+8;
  dw6v=4;
  mh=13;
  n=n0e;
  jn7=n0e;
  j=6;

  while (rw>0&&la>0) {
      if (n0e%2==0) {
          rw = rw - 1;
      }
      else {
          la -= 1;
      }
      n0e++;
      if ((n0e%8)==0) {
          jn7 = jn7 + n0e;
      }
      mh = mh + la;
      n = n + rw;
      dw6v = dw6v + la;
      r = r + la;
      j += 2;
      dw6v++;
  }

}
