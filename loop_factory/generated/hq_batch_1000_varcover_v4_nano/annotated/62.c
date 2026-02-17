int main1(int a,int n,int p){
  int l, i, v, z;

  l=20;
  i=l;
  v=n;
  z=i;

  
  /*@

    loop invariant v == n + (l - i);

    loop invariant z == i;

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant n == \at(n, Pre);

    loop assigns v, z, i;

    loop variant i;

  */
while (i>0) {
      v = v+1;
      z = z-1;
      i = i-1;
  }

}