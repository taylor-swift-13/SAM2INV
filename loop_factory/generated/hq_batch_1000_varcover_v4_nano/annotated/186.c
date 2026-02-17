int main1(int b,int p,int q){
  int l, i, v;

  l=9;
  i=0;
  v=-1;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i && i <= l;
    loop invariant (i == 0) ==> (v == -1);
    loop invariant (b == \at(b, Pre) && q == \at(q, Pre));
    loop assigns i, v;
  */
while (i<l) {
      if ((i%4)==0) {
          v = v+v;
      }
      else {
          v = q+b;
      }
      i = i+1;
  }

}