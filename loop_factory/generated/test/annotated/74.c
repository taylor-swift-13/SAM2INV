int main1(){
  int v, u3g4;
  v=1+13;
  u3g4=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == 14;
  loop invariant 0 <= u3g4;
  loop invariant u3g4 <= v + 2;
  loop assigns u3g4;
*/
while (u3g4<v) {
      if (u3g4>=v/2) {
          u3g4 += 2;
      }
      u3g4 += 1;
  }
}