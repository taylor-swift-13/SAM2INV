int main1(int a,int m){
  int l, i, v, u;

  l=21;
  i=0;
  v=-8;
  u=-8;

  
  
  
  /*@

  
    loop invariant v == 2*u + 8;

  
    loop invariant i == 0;

  
    loop invariant l == 21;

  
    loop invariant a == \at(a, Pre);

  
    loop invariant m == \at(m, Pre);

  
    loop invariant i <= l;

  
    loop invariant v >= -8;

  
    loop invariant -8 <= u;

  
    loop invariant -8 <= v;

  
    loop invariant i >= 0;


  
    loop invariant l >= 0;

  
    loop invariant i % 5 == 0;

  
    loop invariant u < v + 1;

  
    loop invariant l >= 21;


  
    loop invariant v - 2*u - i/5 == 8;

  
    loop assigns v, u;

  
  */
  while (i<l) {
      v = v+1;
      u = u+1;
      v = v+1;
  }

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
    loop invariant 4*i - 5*l == -105;
    loop invariant v <= u;
    loop invariant i >= 0;
    loop invariant -8 <= v;
    loop invariant -8 <= u;
    loop invariant l >= 0;
    loop assigns i, l, v;
    loop variant u - v;
  */
  while (v<u) {
      i = i+5;
      l = l+4;
      v = v+1;
  }

}