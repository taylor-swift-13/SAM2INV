int main1(int b,int k,int p){
  int l, i, v, h, o, q, z, c;

  l=60;
  i=l;
  v=p;
  h=p;
  o=0;
  q=0;
  z=l;
  c=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant h == 2*v - p;
    loop invariant 0 <= i && i <= l;
    loop invariant (o == 0) || (o == 1);
    loop invariant z <= l;
    loop invariant p == \at(p, Pre);
    loop invariant k == \at(k, Pre);
    loop assigns v, h, o, z, i;
  */
  while (i>0) {
      v = v*2;
      h = h+v;
      o = o%2;
      z = o*o;
      o = o%8;
      i = i-1;
  }

}