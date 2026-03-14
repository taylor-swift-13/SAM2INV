int main1(int s){
  int dm5, umdi, ct, u0j;
  dm5=173;
  umdi=0;
  ct=-2;
  u0j=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == \at(s, Pre) + umdi * ct;
  loop invariant 0 <= umdi <= dm5;
  loop invariant u0j == 8 + umdi * \at(s, Pre) - umdi * (umdi - 1);
  loop invariant u0j == 8 + umdi * \at(s, Pre) + ct * (umdi * (umdi - 1) / 2);
  loop assigns u0j, s, umdi;
*/
while (umdi<dm5) {
      u0j = u0j + s;
      s = s + ct;
      umdi += 1;
  }
}