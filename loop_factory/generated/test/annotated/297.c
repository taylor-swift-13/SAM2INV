int main1(int n,int p){
  int l, i, v;

  l=n+17;
  i=0;
  v=i;

  
  
  
  /*@

  
    loop invariant i == v;

  
    loop invariant l == n + 17;

  
    loop invariant n == \at(n, Pre);

  
    loop invariant p == \at(p, Pre);

  
    loop invariant v == i;

  
    loop invariant l == \at(n, Pre) + 17;

  
    loop invariant i >= 0;

  
    loop invariant v >= 0;

  
    loop invariant i % 5 == 0;

  
    loop invariant 0 <= i;


  
    loop invariant v >= i;


  
    loop invariant i <= v;

  
    loop invariant (v - i) % 2 == 0;

  
    loop assigns v, i;

  
    loop variant l - i;

  
  */
  while (i<l) {
      v = v+1;
      v = v+4;
      i = i+5;
  }

  /*@

    loop invariant l == \at(n, Pre) + 17;
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);



    loop assigns v, i;

    loop variant i;
  */
  while (i>0) {
      v = v+1;
      i = i-1;
  }

}