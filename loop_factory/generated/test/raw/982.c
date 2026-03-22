int main1(){
  int vrn6, dl2, owj, h2, fsl, gh, g;

  vrn6=(1%7)+12;
  dl2=vrn6;
  owj=0;
  h2=0;
  fsl=dl2;
  gh=-1;
  g=1*4;

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
