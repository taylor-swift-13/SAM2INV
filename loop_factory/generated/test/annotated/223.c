int main1(int b,int p){
  int l, i, v, q;

  l=p;
  i=1;
  v=i;
  q=p;

  
  /*@

    loop invariant 2*v == 5*i - 3;

    loop invariant i >= 1;

    loop invariant l == \at(p, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant l == p;

    loop invariant i > 0;


    loop invariant v >= 1;

    loop invariant v >= 2*i - 1;

    loop invariant v > 0;

    loop invariant b == \at(b, Pre);

    loop invariant v >= i;

    loop invariant i % 2 == 1;

    loop assigns v, i;

  */
while (i<l) {
      v = v*3+3;
      i = i*3;
  }

}