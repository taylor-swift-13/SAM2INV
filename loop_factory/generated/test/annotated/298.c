int main1(int b,int n){
  int l, i, v;

  l=(n%13)+12;
  i=0;
  v=-3;

  
  
  
  /*@

  
    loop invariant (i == 0) ==> (v == -3);

  
    loop invariant i >= 0;

  
    loop invariant i <= l;

  
    loop invariant l == (\at(n, Pre) % 13) + 12;

  
    loop invariant b == \at(b, Pre);

  
    loop invariant n == \at(n, Pre);

  
    loop invariant 0 <= i && i <= l;

  
    loop invariant n == \at(n, Pre) && b == \at(b, Pre);

  
    loop invariant v <= 0;

  
    loop invariant (i == 0 ==> v == -3) && (i > 0 ==> v == 0);

  
    loop invariant l == (\at(n,Pre) % 13) + 12;

  
    loop invariant n == \at(n,Pre);

  
    loop invariant b == \at(b,Pre);

  
    loop invariant 0 <= i <= l;

  
    loop invariant n == \at(n,Pre) && b == \at(b,Pre);


  
    loop assigns i, v;

  
  */
  while (i<l) {
      v = i-i;
      i = i+1;
  }

  /*@
    loop invariant b == \at(b, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant l == (\at(n, Pre) % 13) + 12;

    loop invariant (i == l) || (i == 5);

    loop assigns i, v;
  */
while (v<l) {
      i = i-i;
      i = i+5;
      v = v*2;
  }

}