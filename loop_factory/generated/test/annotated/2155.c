int main1(){
  int f6o, yzv, q01, v46p, eu3s;
  f6o=1*2;
  yzv=0;
  q01=0;
  v46p=0;
  eu3s=yzv;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant eu3s == f6o * yzv;
  loop invariant (0 <= yzv && yzv <= (f6o * f6o));
  loop invariant (0 <= v46p && v46p < f6o);
  loop invariant (0 <= q01 && q01 <= f6o - 1);
  loop invariant f6o > 0;
  loop invariant (yzv == 0) ==> (q01 == 0 && v46p == 0);
  loop invariant (yzv > 0) ==> ((yzv - 1) == q01 * f6o + v46p);
  loop invariant (q01 * f6o + v46p == yzv) || (q01 * f6o + v46p == (yzv - 1));
  loop assigns q01, v46p, yzv, eu3s;
*/
while (yzv < f6o * f6o) {
      q01 = yzv / f6o;
      v46p = yzv - q01 * f6o;
      yzv++;
      eu3s = eu3s + f6o;
  }
}