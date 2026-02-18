int main1(int n,int q){
  int l, i, v;

  l=28;
  i=1;
  v=-6;

  
  /*@

    loop invariant n == \at(n, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant l == 28;

    loop invariant i <= 2*l;

    loop invariant i > 0;

    loop invariant v % 2 == 0;


    loop invariant v >= -6;

    loop invariant i >= 1;

    loop assigns i, v;

  */
while (i<l) {
      v = v+v;
      v = v*v+v;
      i = i*2;
  }

}