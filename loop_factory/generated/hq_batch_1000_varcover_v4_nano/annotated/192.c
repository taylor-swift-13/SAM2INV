int main1(int a,int b,int m){
  int l, i, v;

  l=28;
  i=0;
  v=m;

  
  /*@

    loop invariant 0 <= i && i <= l;

    loop invariant (i==0 && v==\at(m,Pre)) || (i>0 && v == b + a + 1);

    loop invariant a == \at(a,Pre) && b == \at(b,Pre) && m == \at(m,Pre);

    loop assigns i, v;

    loop variant l - i;

  */
while (i<l) {
      if (i+3<=b+l) {
          v = v+6;
      }
      v = v+i;
      v = v+1;
      v = b+a;
      v = v+1;
      i = i+1;
  }

}