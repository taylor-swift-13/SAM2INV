int main1(){
  int of, aa6, uo, og;
  of=26;
  aa6=0;
  uo=of;
  og=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant og == 6;
  loop invariant 0 <= aa6 && aa6 <= of && aa6 % 2 == 0 && (uo == 26 || uo == 6);
  loop invariant of == 26;
  loop assigns aa6, uo, og;
*/
while (aa6<=of-1) {
      aa6 += 2;
      if (!(!(og<=uo))) {
          uo = og;
      }
      og = og+uo-uo;
  }
}