int main1(int l,int k){
  int hx, q1v, by, p, ubk, fa;

  hx=80;
  q1v=0;
  by=0;
  p=0;
  ubk=l;
  fa=0;

  while (p<hx) {
      by += l;
      p++;
      ubk = ubk+hx-q1v;
      fa = fa+(p%4);
  }

  while (by<ubk) {
      by = by + 1;
      fa += l;
      l = l + by;
      l = l*2;
  }

}
