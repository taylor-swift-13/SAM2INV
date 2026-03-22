int main1(){
  int bx, mr, jp, ut, bqk;

  bx=(1%18)+7;
  mr=0;
  jp=(1%40)+2;
  ut=0;
  bqk=mr;

  while (1) {
      if (!(jp!=ut)) {
          break;
      }
      ut = jp;
      jp = (jp+bx/jp)/2;
      bqk = bqk+ut-jp;
  }

}
