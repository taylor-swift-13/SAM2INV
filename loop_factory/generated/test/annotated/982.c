int main1(){
  int vrn6, dl2, owj, h2, fsl, gh, g;
  vrn6=(1%7)+12;
  dl2=vrn6;
  owj=0;
  h2=0;
  fsl=dl2;
  gh=-1;
  g=1*4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h2 == owj*(owj-1)/2;
  loop invariant fsl == dl2 + owj;
  loop invariant g == 4 + owj*(owj+1)/2;
  loop invariant gh == -1 + owj*dl2 + owj*(owj+1)/2;
  loop invariant (dl2 == vrn6);
  loop invariant (fsl == 13 + owj);
  loop invariant 0 <= owj;
  loop invariant owj <= vrn6;
  loop assigns h2, owj, g, fsl, gh;
*/
while (1) {
      if (!(owj<=vrn6-1)) {
          break;
      }
      h2 += owj;
      owj = owj + 1;
      g += owj;
      fsl++;
      gh = gh + fsl;
      if ((dl2%2)==0) {
          gh = gh + 1;
      }
  }
}