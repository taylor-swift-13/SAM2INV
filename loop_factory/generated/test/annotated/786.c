int main1(){
  int ck, c, gh, h3, fp;
  ck=1;
  c=-2;
  gh=0;
  h3=-3;
  fp=c;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c <= ck;
  loop invariant c >= -2;
  loop invariant gh == 0;
  loop invariant ((c == -2) ==> (h3 == -3)) &&
                     ((c == -1) ==> (h3 == 9))  &&
                     ((c == 0)  ==> (h3 == 81));
  loop invariant h3 >= -3;
  loop assigns h3, gh, c;
*/
while (1) {
      if (!(c<=ck-1)) {
          break;
      }
      h3 = h3*h3+gh;
      gh = gh%6;
      gh = gh*fp;
      c = c + 1;
  }
}