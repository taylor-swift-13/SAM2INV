int main1(){
  int v9, jck, p;
  v9=(1%32)+14;
  jck=v9;
  p=(1%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v9 == 1 % 32 + 14;
  loop invariant jck >= 1 % 32 + 14;
  loop invariant p - 5*jck == -66;
  loop assigns jck, p;
*/
while (p>0&&p>0) {
      if (jck%2==0) {
          p -= 1;
      }
      else {
          p -= 1;
      }
      jck = jck + 1;
      p += 6;
  }
}