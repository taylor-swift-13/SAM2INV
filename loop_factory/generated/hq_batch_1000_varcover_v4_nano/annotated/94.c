int main1(int b,int k,int p){
  int l, i, v, j, q, h, x, r, z, w;

  l=59;
  i=1;
  v=k;
  j=b;
  q=k;
  h=l;
  x=-1;
  r=l;
  z=k;
  w=k;

  
  /*@

    loop invariant k == \at(k, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant v == k * i;

    loop invariant j == b + 2 * k * (i - 1);

    loop invariant 1 <= i && i <= 2 * l;

    loop assigns v, j, i;

  */
while (i<l) {
      v = v*2;
      j = j+v;
      i = i*2;
  }

}