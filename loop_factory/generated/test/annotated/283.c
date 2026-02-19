int main1(int n,int q){
  int l, i, v;

  l=70;
  i=l;
  v=0;

  
  
  
  
  
  
  
  /*@

  
  
  
    loop invariant v == 0;

  
  
  
    loop invariant i >= 0;

  
  
  
    loop invariant i <= 70;

  
  
  
    loop invariant l == 70;

  
  
  
    loop invariant n == \at(n, Pre);

  
  
  
    loop invariant q == \at(q, Pre);

  
  
  
    loop invariant v >= 0;

  
  
  
    loop invariant n == \at(n,Pre);

  
  
  
    loop invariant q == \at(q,Pre);

  
  
  
    loop invariant l >= 0;

  
  
  
    loop invariant l == 70 || l == 0;

  
  
  
    loop invariant i + v*(v+1)/2 >= 0;



  
  
  
    loop assigns i, v;

  
  
  
  */
  while (i>0) {
      v = v+v;
      i = i-1;
  }

  /*>>> LOOP INVARIANT TO FILL <<<*/
  /*@
    loop invariant n == \at(n, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant v == 0;
    loop invariant i >= 0;
    loop invariant l == 0 || l == 70;
    loop invariant i % 4 == 0;
    loop assigns i, l;
  */
while (v>0) {
      i = i+v;
      v = v-1;
  }

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
    loop invariant n == \at(n, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant v == 0;
    loop invariant i >= 0;
    loop invariant l == 0 || l == 70;
    loop invariant i % 4 == 0;
    loop assigns i, l;
  */
while (i<v) {
      l = l-l;
      i = i+4;
  }

}