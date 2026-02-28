int main1(int n,int q){
  int r, f, v;

  r=q+19;
  f=0;
  v=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == \at(q, Pre) + 19;
  loop invariant q == \at(q, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant f >= 0;
  loop invariant v >= 0;


  loop invariant r == q + 19;
  loop invariant (f % 3 == 0) && (0 <= f) && (v >= 0) && ((v - f) == 5 || (v - f) == -2 || (v - f) == -3);

  loop invariant (f == 0 ==> v == 5) && (f != 0 ==> (f - v == 2 || f - v == 3));
  loop invariant f % 3 == 0;
  loop invariant (f == 0 && v == 5) || (f >= 3 && (r >= 4 ==> v == f - 2) && (r < 4 ==> v == f - 3));
  loop assigns f, v;
*/
while (f+3<=r) {
      v = v-v;
      v = v+f;
      if (f+4<=v+r) {
          v = v+1;
      }
      f = f+3;
  }

}
