int main1(int a,int k,int m){
  int l, i, v, o, c, z, d;

  l=17;
  i=l;
  v=4;
  o=a;
  c=k;
  z=i;
  d=k;

    /*@
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant v == l - i + 4;
    loop invariant o == a + 4*(l - i) + ((l - i)*(l - i + 1))/2;
    loop invariant z == 5*l - 4*i;
    loop assigns v, o, z, i;
    loop variant i;
  */
while (i>0) {
      v = v+1;
      o = o+v;
      z = z+4;
      i = i-1;
  }

}