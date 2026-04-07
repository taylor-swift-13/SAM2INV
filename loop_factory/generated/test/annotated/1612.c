int main1(int a){
  int vk, ofl, an, eh4q;
  vk=110;
  ofl=0;
  an=4;
  eh4q=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre) + eh4q * ofl;
  loop invariant eh4q <= vk;
  loop invariant a == \at(a, Pre);
  loop invariant an == 4 + eh4q * \at(a, Pre);
  loop invariant an == 4 + eh4q * a;
  loop invariant 0 <= eh4q;
  loop assigns eh4q, an, a;
*/
while (1) {
      if (!(eh4q<vk)) {
          break;
      }
      eh4q++;
      an = an + a;
      a = a + ofl;
  }
}