int main1(int b,int u){
  int f;
  f=(u%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == \at(u, Pre);
  loop invariant f <= (u % 20) + 5;
  loop invariant ((u % 20) + 5 - f) % 3 == 0;
  loop assigns b, f;
*/
while (f>0) {
      if (f>0) {
          if (f>0) {
              f--;
              f--;
              f--;
          }
      }
      b += f;
  }
}