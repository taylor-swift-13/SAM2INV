int main1(int a,int n,int p,int q){
  int l, i, v, h, g, z, t, c;

  l=25;
  i=l;
  v=-6;
  h=l;
  g=a;
  z=l;
  t=-4;
  c=q;

  
  /*@

    loop invariant 0 <= i && i <= l;

    loop invariant v == -6 || (-5 <= v && v <= 5);

    loop invariant l == 25;

    loop invariant i == l ==> (z == l && v == -6);

    loop invariant a == \at(a,Pre) && n == \at(n,Pre) && p == \at(p,Pre) && q == \at(q,Pre);

    loop assigns i, v, z;

    loop variant i;

  */
while (i>0) {
      z = z*z+v;
      v = v%6;
      i = i-1;
  }

}