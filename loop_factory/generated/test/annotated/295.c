int main1(int k,int q){
  int l, i, v;

  l=13;
  i=l;
  v=k;

  
  
  
  /*@

  
    loop invariant k == \at(k, Pre);

  
    loop invariant q == \at(q, Pre);

  
    loop invariant l == 13;

  
    loop invariant 0 <= i && i <= 13;

  
    loop invariant v >= k;

  
    loop invariant i >= 0;

  
    loop invariant i <= 13;

  
    loop invariant k == \at(k,Pre);

  
    loop invariant q == \at(q,Pre);

  
    loop invariant v - k == 23 - (i + i/2 + i/4 + i/8 + i/16);

  
    loop invariant 0 <= i <= 13;

  
    loop invariant 0 <= i;


  
    loop invariant 13 <= l;


  
    loop assigns i, v;

  
    loop variant i;

  
  */
  while (i>0) {
      v = v+i;
      i = i/2;
  }

  /*@
    loop invariant k == \at(k, Pre);
    loop invariant q == \at(q, Pre);

    loop invariant 0 <= i;
    loop assigns i, l;
    loop variant v - l;
  */
  while (l<v) {
      i = i+1;
      l = l+1;
  }

}