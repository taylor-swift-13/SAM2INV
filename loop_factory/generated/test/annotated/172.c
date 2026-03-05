int main1(){
  int nh, c9f;
  nh=1;
  c9f=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant nh == 1;
  loop invariant (c9f - 1) % 3 == 0;
  loop invariant c9f >= 1;
  loop invariant c9f <= nh + 3;
  loop assigns c9f;
*/
while (c9f<=nh) {
      c9f = c9f + 1;
      c9f += 2;
  }
}