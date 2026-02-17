int main1(int m,int n,int p){
  int l, i, v, f;

  l=47;
  i=0;
  v=p;
  f=l;

  
  /*@

    loop invariant v == \at(p, Pre) + i;

    loop invariant f == l + i * \at(p, Pre) + (i*(i+1))/2;

    loop invariant 0 <= i && i <= l;

    loop assigns i, v, f;

    loop variant l - i;

  */
while (i<l) {
      v = v+1;
      f = f+v;
      i = i+1;
  }

}