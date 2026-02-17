int main1(int a,int b,int p){
  int l, i, v, r, z, f;

  l=60;
  i=l;
  v=b;
  r=b;
  z=1;
  f=0;

  
  /*@

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant 2*v == r*r - b*b - r + 3*b;

    loop invariant r >= b;

    loop invariant i >= 0;

    loop invariant i <= l;


    loop assigns v, r, i;

  */
  while (i>0) {
      v = v+r;
      r = r+z;
      i = i/2;
  }

}