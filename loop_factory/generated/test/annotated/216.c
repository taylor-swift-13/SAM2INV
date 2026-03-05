int main1(){
  int sd, r;
  sd=1;
  r=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r % 4 == 0;
  loop invariant r >= 0;
  loop invariant sd == 1;
  loop invariant r <= 4;
  loop assigns r;
*/
while (r<sd) {
      r = r + 3;
      r = r + 1;
  }
}