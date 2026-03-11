int main1(){
  int q, b, kfn, p2, xmn, t;

  q=1-4;
  b=q+5;
  kfn=3;
  p2=0;
  xmn=4;
  t=b;

  while (1) {
      if (!(p2<=q-1)) {
          break;
      }
      kfn++;
      p2 = p2 + 1;
      xmn = xmn + kfn;
      t += b;
  }

  while (xmn<kfn) {
      p2 = p2 + 1;
      xmn = xmn + 1;
      if ((t%8)==0) {
          p2 = p2*2;
      }
  }

}
