int main1(){
  int jp, et, mo, yb3, tw;

  jp=67;
  et=jp;
  mo=0;
  yb3=(1%28)+10;
  tw=11;

  while (1) {
      if (!(yb3>mo)) {
          break;
      }
      yb3 -= mo;
      tw = tw+jp-et;
      mo++;
  }

}
