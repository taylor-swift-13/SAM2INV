int main1(int a){
  int iu, xy;
  iu=68;
  xy=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant iu == 68;
  loop invariant xy % 2 == 0;
  loop invariant 0 <= xy;
  loop invariant xy <= iu;
  loop assigns xy, a;
*/
while (xy<iu) {
      if (xy%10==0) {
          xy++;
      }
      else {
          if (xy%6==0) {
              xy++;
          }
          else {
              if (xy%7==0) {
                  xy++;
              }
              else {
                  xy++;
              }
          }
      }
      xy++;
      a = (a+xy)%7;
  }
}