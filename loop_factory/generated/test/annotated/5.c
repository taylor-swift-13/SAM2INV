int main1(int u){
  int u7c;
  u7c=18;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u7c == 18;
  loop invariant u == \at(u, Pre);
  loop assigns u7c;
*/
while (u7c>0) {
      u7c++;
      u7c -= 1;
  }
}