int main1(){
  int v, n, oe, f, bn;

  v=1+25;
  n=0;
  oe=1;
  f=0;
  bn=v;

  while (oe<=v) {
      f = f+oe*oe;
      oe += 1;
      bn += n;
  }

  for (; v<=f-1; v++) {
      oe = oe+(-4);
      oe += 6;
  }

}
