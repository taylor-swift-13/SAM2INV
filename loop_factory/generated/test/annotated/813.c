int main1(){
  int sk, wat, ml9, e;
  sk=1+25;
  wat=0;
  ml9=wat;
  e=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ml9 == 0;
  loop invariant e == 3;
  loop invariant wat <= sk;
  loop invariant (wat == 0) || (wat == sk);
  loop assigns e, wat;
*/
while (wat<sk) {
      e += ml9;
      wat = sk;
  }
}