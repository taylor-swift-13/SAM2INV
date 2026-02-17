int main1(int k,int p,int q){
  int l, i, v, a, w, o, r;

  l=p;
  i=0;
  v=-2;
  a=3;
  w=-1;
  o=5;
  r=k;

  
  /*@

    loop invariant l == \at(p, Pre);

    loop invariant (o == v + a + w) || i == 0;

    loop invariant 0 <= i;

    loop invariant i <= l || l <= 0;

    loop assigns o, i;

  */
while (i<l) {
      o = v+a+w;
      i = i+1;
  }

}