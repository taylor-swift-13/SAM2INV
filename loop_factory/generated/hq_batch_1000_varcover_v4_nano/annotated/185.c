int main1(int a,int b,int m){
  int l, i, v, g, j, x;

  l=a;
  i=0;
  v=m;
  g=-2;
  j=l;
  x=5;

  
  /*@

    loop invariant l == \at(a, Pre);

    loop invariant 0 <= i;

    loop invariant (l >= 0) ==> i <= l;

    loop invariant (i == 0) ==> (v == \at(m, Pre) && g == -2 && j == l);

    loop invariant (i > 0) ==> j == g * g;

    loop invariant (i > 0) ==> ((v + 1) % 3 == 0);

    loop assigns v, g, j, i;

  */
while (i<l) {
      v = v*3+2;
      g = g*v+2;
      j = g*g;
      i = i+1;
  }

}