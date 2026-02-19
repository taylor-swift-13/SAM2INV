int main1(int p,int q){
  int l, i, v;

  l=q+6;
  i=0;
  v=l;

  
  
  
  /*@

  
    loop invariant l == \at(q, Pre) + 6;

  
    loop invariant p == \at(p, Pre);

  
    loop invariant q == \at(q, Pre);

  
    loop invariant l == q + 6;

  
    loop invariant (l >= 0) ==> (0 <= i && i <= l);

  
    loop invariant (l >= 0) ==> (v >= l);

  
    loop invariant v >= l;

  
    loop invariant i >= 0;

  
    loop invariant l == \at(q,Pre) + 6;

  
    loop invariant q == \at(q,Pre);

  
    loop invariant p == \at(p,Pre);

  
    loop invariant 0 <= i;





  
    loop assigns v, i;

  
  */
  while (i<l) {
      v = v+v;
      v = v+i;
      i = i+1;
  }

  /*@
    loop invariant l == \at(q, Pre) + 6;
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant i >= 0;


    loop assigns i, v;
    loop variant l - v;
  */
while (v<l) {
      i = i+i;
      v = v*3;
  }

}