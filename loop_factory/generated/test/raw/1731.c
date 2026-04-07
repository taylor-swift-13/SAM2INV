int main1(){
  int mga, py, w;

  mga=28;
  py=0;
  w=0;

  while (w<mga) {
      w += 1;
      py = (py+1)%3;
      py = py - py;
  }

}
