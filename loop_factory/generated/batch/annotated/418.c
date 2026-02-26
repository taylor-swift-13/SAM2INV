int main1(int k,int n){
  int v, e, a;

  v=k+8;
  e=1;
  a=e;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == \at(k, Pre) + 8;
  loop invariant e == 1;
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant 0 <= a;
  loop invariant a <= 2;
  loop invariant 0 <= a <= 2;
  loop invariant a >= 0;
  loop invariant v == k + 8;
  loop invariant a <= 6;
  loop invariant (a == 0) || (a == 1) || (a == 2) || (a == 6);
  loop assigns a;
*/
while (e*3<=v) {
      a = a+2;
      a = a%3;
      if ((e%5)==0) {
          a = a*a+a;
      }
  }

}
