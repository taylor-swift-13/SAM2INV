int main1(int r){
  int v1h, w3, ret, lt, dog;
  v1h=(r%7)+17;
  w3=0;
  ret=0;
  lt=0;
  dog=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == (\at(r, Pre) + dog * w3);
  loop invariant ret == 3 * w3;
  loop invariant lt == w3;
  loop invariant 0 <= w3;
  loop invariant w3 <= v1h;
  loop invariant v1h == ((\at(r, Pre) % 7) + 17);
  loop invariant (dog == 0);
  loop assigns ret, r, w3, lt;
*/
while (w3 < v1h) {
      ret = ret + 3;
      r += dog;
      w3 += 1;
      lt += 1;
  }
}