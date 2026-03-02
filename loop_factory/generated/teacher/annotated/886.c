int main1(int n,int p){
  int b, k, v;

  b=57;
  k=0;
  v=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == 57;
  loop invariant v == 57 || (0 <= v && v < 5);
  loop invariant k >= 0;
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant v == b || v == b%5;
  loop invariant (v == b) || (0 <= v && v <= 4);
  loop invariant (k == 0) ==> (v == 57);
  loop invariant (v == 57) <==> (k == 0);
  loop invariant 0 <= v && v <= 57;
  loop invariant (v == 57) || (0 <= v && v <= 4);
  loop invariant (k == 0 ==> v == 57) && (k >= 1 ==> v == 57 % 5);
  loop invariant (k >= 1 ==> 0 <= v <= 4);
  loop invariant (k == 0 && v == b) || (k >= 1 && 0 <= v && v < 5 && v == b % 5);
  loop invariant n == \at(n, Pre) && p == \at(p, Pre) && b == 57;
  loop invariant n == \at(n, Pre) && p == \at(p, Pre) && b == 57 && 0 <= v <= b;
  loop invariant v == 57 || v == 2;
  loop invariant (k >= 0) && (v >= 0) && (v <= 57) && (b == 57) && (n == \at(n,Pre)) && (p == \at(p,Pre));
  loop invariant (n == \at(n,Pre));
  loop assigns v, k;
*/
while (1) {
      v = v%5;
      k = k+1;
  }

}
