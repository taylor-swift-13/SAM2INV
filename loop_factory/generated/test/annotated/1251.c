int main1(){
  int jk9, tp4, c, h, kb;
  jk9=59;
  tp4=jk9+4;
  c=jk9;
  h=0;
  kb=jk9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h >= 0;
  loop invariant c == 59 + h*(h+1)*(2*h+1)/6;
  loop invariant (h == 0) ==> (jk9 == 59);
  loop invariant kb >= 59;
  loop invariant tp4 - jk9 >= 1;
  loop assigns h, c, kb, jk9;
*/
while (tp4-jk9>0) {
      h += 1;
      c = c+h*h;
      kb = kb + c;
      kb = kb*2;
      jk9 = 0;
  }
}