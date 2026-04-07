int main1(int o){
  int rs, yu, pxx4, pi;
  rs=32;
  yu=0;
  pxx4=-6;
  pi=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yu == pi;
  loop invariant 0 <= pi <= rs;
  loop invariant (pxx4 == -6) || (pxx4 == yu - 1);
  loop assigns pi, pxx4, yu;
*/
while (yu+1<=rs) {
      if (pi<rs) {
          pxx4 = yu;
      }
      pi++;
      yu++;
  }
}