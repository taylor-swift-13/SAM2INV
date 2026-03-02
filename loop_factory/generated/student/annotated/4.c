int main1(int a,int n){
  int b, u, v;

  b=74;
  u=0;
  v=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u >= 0;
  loop invariant v >= 8;
  loop invariant u == 0;
  loop assigns v;
*/
while (1) {
      v = v+4;
      if ((u%7)==0) {
          v = v+1;
      }
      else {
          v = v+v;
      }
  }

}
