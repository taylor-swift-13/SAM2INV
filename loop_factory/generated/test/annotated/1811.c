int main1(){
  int lkn, o48u, k1, q9, vk, v6;
  lkn=1*3;
  o48u=1;
  k1=0;
  q9=(1%28)+10;
  vk=25;
  v6=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q9 + (k1*(k1 - 1))/2 == 11;
  loop invariant vk == 25 + 15*(k1/6) + ((k1%6)*((k1%6) + 1))/2;
  loop invariant lkn == 3;
  loop invariant o48u == 1;
  loop invariant v6 == 3 + 2*k1;
  loop invariant k1 >= 0;
  loop invariant q9 >= 0;
  loop assigns q9, k1, vk, v6;
*/
while (q9>k1) {
      q9 -= k1;
      k1 = k1 + 1;
      vk = vk+(k1%6);
      v6 = v6+lkn-o48u;
  }
}