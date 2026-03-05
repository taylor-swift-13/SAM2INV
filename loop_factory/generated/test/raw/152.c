int main1(){
  int mp8;

  mp8=0;

  while (mp8!=0) {
      if (mp8%2==1) {
          mp8 = mp8 + mp8;
          mp8 -= 1;
      }
      else {
      }
      mp8 = 2*mp8;
      mp8 = mp8/2;
  }

}
