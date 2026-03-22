int main1(){
  int ljm2, rjsu, gt;

  ljm2=(1%31)+16;
  rjsu=-1;
  gt=rjsu;

  while (1) {
      if (!(rjsu<=ljm2-1)) {
          break;
      }
      gt = gt*3;
      rjsu += 1;
  }

}
