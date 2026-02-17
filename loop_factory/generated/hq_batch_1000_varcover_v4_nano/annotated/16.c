int main1(int a,int k,int m){
  int l, i, v, f, x, h, u, s, z, w;

  l=13;
  i=0;
  v=-6;
  f=i;
  x=i;
  h=m;
  u=3;
  s=m;
  z=k;
  w=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 13;
  loop invariant 0 <= i && i <= l;
  loop invariant i == 0 ==> h == \at(m,Pre);
  loop invariant i == 0 ==> v == -6;
  loop invariant i >= 1 ==> v == v%6;
  loop assigns h, v, i;
  loop variant l - i;
*/
while (i<l) {
      h = h*h+v;
      v = v%6;
      i = i+1;
  }

}