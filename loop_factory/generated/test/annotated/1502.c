int main1(){
  int es, bt9, d, pb, o1;
  es=5;
  bt9=0;
  d=bt9;
  pb=es;
  o1=13;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant es == 5;
  loop invariant d == 0;
  loop invariant 0 <= bt9;
  loop invariant bt9 <= es;
  loop invariant o1 >= 13;
  loop invariant pb >= 5;
  loop assigns bt9, d, pb, o1;
*/
while (bt9 < es) {
      bt9++;
      d = d * o1;
      pb = pb * o1;
      o1 = o1*2+(d%4)+0;
  }
}