int main1(int a,int q){
  int l, i, v;

  l=68;
  i=l;
  v=a;

  
  
  
  /*@

  
    loop invariant i >= 0;

  
    loop invariant i <= 68;

  
    loop invariant a == \at(a, Pre);

  
    loop invariant q == \at(q, Pre);

  
    loop invariant l == 68;

  
    loop invariant 2*v == 2*a + (68 - i) * (i + 73);

  
    loop invariant v == a + 2482 - (i*i + 5*i)/2;

  
    loop invariant v >= \at(a, Pre);

  
    loop invariant v == \at(a, Pre) + 70*(68 - i) - (((68 - i) * (67 - i)) / 2);

  
    loop invariant l >= 0;



  
    loop invariant v >= a;

  
    loop invariant l >= 68;

  
    loop assigns v, i;

  
    loop variant i;

  
  */
  while (i>0) {
      v = v+i;
      v = v+2;
      i = i-1;
  }

  /*@
    loop invariant l >= 0;

    loop invariant a == \at(a, Pre);
    loop invariant q == \at(q, Pre);
    loop assigns v, l;
    loop variant i - l;
  */
  while (l<i) {
      v = v+l;
      v = v+v;
      l = l+1;
  }

}