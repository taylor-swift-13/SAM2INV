int main1(){
  int q, c, j, qx;

  q=1-10;
  c=0;
  j=0;
  qx=q;

  while (j<q) {
      c = (c+1)%4;
      j++;
      qx = qx + q;
      qx += 2;
  }

}
