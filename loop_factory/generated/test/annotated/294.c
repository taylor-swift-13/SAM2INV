int main1(int m,int n){
  int l, i, v;

  l=23;
  i=0;
  v=n;

  
  
  
  /*@

  
    loop invariant i % 4 == 0;

  
    loop invariant (i > 0) ==> (v == 0);

  
    loop invariant (i == 0) ==> (v == n);

  
    loop invariant i <= l + 1;

  
    loop invariant l == 23;

  
    loop invariant n == \at(n, Pre);

  
    loop invariant m == \at(m, Pre);

  
    loop invariant 0 <= i && i <= l + 3;

  
    loop invariant (v == 0) || (i == 0 && v == \at(n, Pre));

  
    loop invariant (i == 0 && v == \at(n, Pre)) || (i >= 4 && v == 0);

  
    loop invariant m == \at(m, Pre) && n == \at(n, Pre);

  
    loop invariant (i == 0 ==> v == \at(n, Pre)) && (i != 0 ==> v == 0);

  
    loop invariant i >= 0;

  
    loop invariant i <= l + 3;

  
    loop invariant v == 0 || v == \at(n, Pre);


  
    loop invariant (l == 23);



  
    loop invariant 0 <= i;

  
    loop assigns i, v;

  
    loop variant l - i;

  
  */
  while (i<l) {
      v = v-v;
      v = v+v;
      i = i+4;
  }

  /*>>> LOOP INVARIANT TO FILL<<< */
  /*@
    loop invariant i > l;
    loop invariant i % 24 == 0;
    loop invariant v % 5 == 0;
    loop invariant l == 23;
    loop invariant m == \at(m, Pre) && n == \at(n, Pre);
    loop assigns i, v;
    loop variant l - v;
  */
  while (v<l) {
      i = i+i;
      v = v+5;
  }

}