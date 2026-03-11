int main1(){
  int l1jm, m, oh, ah;
  l1jm=1;
  m=2;
  oh=0;
  ah=m;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ah + oh == l1jm + 1;
  loop invariant 0 <= oh;
  loop invariant oh <= l1jm;
  loop assigns ah, oh;
*/
while (oh<=l1jm-1) {
      oh += 1;
      ah = l1jm-oh;
      ah = ah + 1;
  }
}