int main1(){
  int i4h, o4, sqho;

  i4h=1+20;
  o4=0;
  sqho=0;

  while (1) {
      if (!(o4 < i4h)) {
          break;
      }
      sqho = 1 - sqho;
      o4++;
      if ((o4%3)==0) {
          sqho = sqho + o4;
      }
  }

}
