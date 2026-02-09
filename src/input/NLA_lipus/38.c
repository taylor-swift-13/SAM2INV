/*@ requires n > 0;*/
int main1(){

  int n, guess, prev_guess;
  
  guess = n / 2;
  prev_guess = 0;

  while (guess != prev_guess) {
        prev_guess = guess;
        guess = (guess + n / guess) / 2;  
    }
  /*@ assert (guess + 1) * (guess + 1) > n;*/
}

