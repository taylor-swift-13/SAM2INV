int main1(int p){
  int fp;

  fp=(p%15)+3;

  while (fp!=0) {
      fp -= 1;
      p += fp;
  }

}
